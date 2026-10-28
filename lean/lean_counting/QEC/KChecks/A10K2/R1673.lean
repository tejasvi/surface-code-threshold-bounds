import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6692 = true := by
  decide +kernel

theorem tot6692 : totK PA10K2 A10K2.t6692 = [0, 0, 0, 713025505943, 2023685064218, 1574701570615, 379008486577, 25239774317, 0, 0] := by
  decide +kernel

theorem rows6693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6693 = true := by
  decide +kernel

theorem tot6693 : totK PA10K2 A10K2.t6693 = [0, 0, 282200127425, 1240333416464, 1822170306592, 1026100028380, 165427985035, 5365973533, 0, 0] := by
  decide +kernel

theorem rows6694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6694 = true := by
  decide +kernel

theorem tot6694 : totK PA10K2 A10K2.t6694 = [0, 0, 293216786569, 1434602533118, 2021013995011, 732961364474, 48003952708, 0, 0, 0] := by
  decide +kernel

theorem rows6695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6695 = true := by
  decide +kernel

theorem tot6695 : totK PA10K2 A10K2.t6695 = [0, 0, 295411761641, 1263120660521, 1884214486284, 1012338972357, 170162482128, 5528811039, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
