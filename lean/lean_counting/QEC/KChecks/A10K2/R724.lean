import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2896 = true := by
  decide +kernel

theorem tot2896 : totK PA10K2 A10K2.t2896 = [0, 108972299072, 660995036886, 1759676782410, 1695319134295, 468801467419, 30650496230, 0, 0, 0] := by
  decide +kernel

theorem rows2897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2897 = true := by
  decide +kernel

theorem tot2897 : totK PA10K2 A10K2.t2897 = [0, 424805370286, 1612102672046, 1963305644676, 726188562368, 58999682306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2898 = true := by
  decide +kernel

theorem tot2898 : totK PA10K2 A10K2.t2898 = [0, 540666301456, 2043010980245, 2071459204918, 510546036369, 27069190465, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2899 = true := by
  decide +kernel

theorem tot2899 : totK PA10K2 A10K2.t2899 = [312139800791, 1099704175298, 1543125587955, 1352679940207, 558473670339, 50548650670, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
