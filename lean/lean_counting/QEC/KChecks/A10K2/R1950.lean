import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7800 = true := by
  decide +kernel

theorem tot7800 : totK PA10K2 A10K2.t7800 = [0, 0, 0, 471121920352, 1828630252998, 2071656412500, 586053479694, 23361545837, 0, 0] := by
  decide +kernel

theorem rows7801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7801 = true := by
  decide +kernel

theorem tot7801 : totK PA10K2 A10K2.t7801 = [0, 0, 554885253651, 1861461451316, 1702190087534, 482323337773, 143170975347, 31681621791, 0, 0] := by
  decide +kernel

theorem rows7802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7802 = true := by
  decide +kernel

theorem tot7802 : totK PA10K2 A10K2.t7802 = [0, 0, 292098887399, 1439587498156, 2184374380311, 901036125450, 67727243258, 0, 0, 0] := by
  decide +kernel

theorem rows7803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7803 = true := by
  decide +kernel

theorem tot7803 : totK PA10K2 A10K2.t7803 = [0, 0, 0, 501007549575, 1787453284393, 1794358636692, 488729280922, 30831673886, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
