import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4904 = true := by
  decide +kernel

theorem tot4904 : totK PD2M8K2 D2M8K2.t4904 = [0, 0, 167115188431, 482009558732, 256103527344, 13916467904, 0, 0] := by
  decide +kernel

theorem rows4905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4905 = true := by
  decide +kernel

theorem tot4905 : totK PD2M8K2 D2M8K2.t4905 = [0, 0, 0, 276339924711, 512180715831, 101474097021, 1096505104, 0] := by
  decide +kernel

theorem rows4906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4906 = true := by
  decide +kernel

theorem tot4906 : totK PD2M8K2 D2M8K2.t4906 = [0, 0, 0, 213182820437, 493066604653, 167683175671, 5253830308, 0] := by
  decide +kernel

theorem rows4907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4907 = true := by
  decide +kernel

theorem tot4907 : totK PD2M8K2 D2M8K2.t4907 = [0, 0, 0, 222618645615, 475386007871, 165090764561, 4470216568, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
