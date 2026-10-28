import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6628 = true := by
  decide +kernel

theorem tot6628 : totK PA10K2 A10K2.t6628 = [0, 547114737165, 1892961818916, 1865816841357, 515031404053, 32035867417, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6629 = true := by
  decide +kernel

theorem tot6629 : totK PA10K2 A10K2.t6629 = [0, 119585100515, 1037639702588, 2152464160431, 1385121141362, 273505954585, 20300850681, 0, 0, 0] := by
  decide +kernel

theorem rows6630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6630 = true := by
  decide +kernel

theorem tot6630 : totK PA10K2 A10K2.t6630 = [0, 251429758060, 1015204856196, 1823693220584, 1449804234669, 319861534368, 11151418702, 0, 0, 0] := by
  decide +kernel

theorem rows6631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6631 = true := by
  decide +kernel

theorem tot6631 : totK PA10K2 A10K2.t6631 = [0, 419288264077, 1769340027913, 2109701215481, 648422479838, 41618034995, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
