/**
 * mdbook の "Suggest an edit" ボタンのリンクが md ファイルへのリンクになっており，
 * そのままだと動作しないので変更する
 */
const editButton = document.querySelector('#git-edit-button');
const editButtonLink = editButton.parentElement;
editButtonLink.href = editButtonLink.href.replace(/\.md$/, '.lean');