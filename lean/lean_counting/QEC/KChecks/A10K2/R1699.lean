import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6796 = true := by
  decide +kernel

theorem tot6796 : totK PA10K2 A10K2.t6796 = [0, 291018669035, 1279815126906, 1919000399945, 1033290469733, 166299157686, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows6797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6797 = true := by
  decide +kernel

theorem tot6797 : totK PA10K2 A10K2.t6797 = [0, 540666301456, 1981383731978, 2122273781611, 570863876097, 19876255495, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6798 = true := by
  decide +kernel

theorem tot6798 : totK PA10K2 A10K2.t6798 = [513260446086, 1600470882321, 1599719363152, 772828060334, 287781146592, 37674914273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6799 = true := by
  decide +kernel

theorem tot6799 : totK PA10K2 A10K2.t6799 = [297779599935, 1535249700250, 2168900430145, 875965614061, 78639266415, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
