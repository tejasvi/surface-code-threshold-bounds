import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7044 = true := by
  decide +kernel

theorem tot7044 : totK PD2M8K2 D2M8K2.t7044 = [0, 0, 0, 248620112588, 448733210408, 130294667632, 4838243418, 0] := by
  decide +kernel

theorem rows7045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7045 = true := by
  decide +kernel

theorem tot7045 : totK PD2M8K2 D2M8K2.t7045 = [0, 0, 174952877924, 456132143129, 253618472063, 29021316005, 0, 0] := by
  decide +kernel

theorem rows7046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7046 = true := by
  decide +kernel

theorem tot7046 : totK PD2M8K2 D2M8K2.t7046 = [0, 0, 173923725752, 458265037640, 250501103055, 14571944896, 0, 0] := by
  decide +kernel

theorem rows7047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7047 = true := by
  decide +kernel

theorem tot7047 : totK PD2M8K2 D2M8K2.t7047 = [0, 0, 93587166913, 362866186960, 363465940278, 67798065712, 1242138600, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
