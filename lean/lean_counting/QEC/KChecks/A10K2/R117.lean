import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t468 = true := by
  decide +kernel

theorem tot468 : totK PA10K2 A10K2.t468 = [0, 0, 491657641739, 1860942504662, 2073418516511, 638411341751, 29503374433, 0, 0, 0] := by
  decide +kernel

theorem rows469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t469 = true := by
  decide +kernel

theorem tot469 : totK PA10K2 A10K2.t469 = [582869944845, 1908502316088, 1739462124985, 450291257098, 69970225556, 72048166685, 26011840508, 0, 0, 0] := by
  decide +kernel

theorem rows470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t470 = true := by
  decide +kernel

theorem tot470 : totK PA10K2 A10K2.t470 = [260421116750, 1416772804658, 2234685718191, 931829881070, 76896867505, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t471 = true := by
  decide +kernel

theorem tot471 : totK PA10K2 A10K2.t471 = [0, 470663058467, 1839161472115, 1942617485666, 512961428183, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
