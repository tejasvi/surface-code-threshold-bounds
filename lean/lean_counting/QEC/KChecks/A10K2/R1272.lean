import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5088 = true := by
  decide +kernel

theorem tot5088 : totK PA10K2 A10K2.t5088 = [0, 281407675879, 1354367716474, 2044537279142, 910496372005, 118536983670, 14516226383, 0, 0, 0] := by
  decide +kernel

theorem rows5089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5089 = true := by
  decide +kernel

theorem tot5089 : totK PA10K2 A10K2.t5089 = [0, 306047774799, 1098254515508, 1672627029644, 1281756874756, 321689250112, 15885829643, 0, 0, 0] := by
  decide +kernel

theorem rows5090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5090 = true := by
  decide +kernel

theorem tot5090 : totK PA10K2 A10K2.t5090 = [0, 475708131122, 1808070614134, 1972757603503, 566212234520, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5091 = true := by
  decide +kernel

theorem tot5091 : totK PA10K2 A10K2.t5091 = [0, 0, 709965739751, 2097878790277, 1650920315791, 387104204229, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
