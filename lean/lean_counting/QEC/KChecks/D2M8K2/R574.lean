import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2296 = true := by
  decide +kernel

theorem tot2296 : totK PD2M8K2 D2M8K2.t2296 = [0, 0, 195509838302, 469322905143, 210778906115, 12595094539, 0, 0] := by
  decide +kernel

theorem rows2297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2297 = true := by
  decide +kernel

theorem tot2297 : totK PD2M8K2 D2M8K2.t2297 = [0, 0, 198361624800, 477549469286, 192615843548, 9724120047, 0, 0] := by
  decide +kernel

theorem rows2298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2298 = true := by
  decide +kernel

theorem tot2298 : totK PD2M8K2 D2M8K2.t2298 = [0, 0, 174830706772, 464663423660, 225068684638, 13772981906, 0, 0] := by
  decide +kernel

theorem rows2299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2299 = true := by
  decide +kernel

theorem tot2299 : totK PD2M8K2 D2M8K2.t2299 = [0, 0, 170004599212, 469393905797, 240805370891, 10929898537, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
