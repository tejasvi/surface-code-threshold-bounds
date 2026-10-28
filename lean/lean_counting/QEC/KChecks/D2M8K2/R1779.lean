import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7116 = true := by
  decide +kernel

theorem tot7116 : totK PD2M8K2 D2M8K2.t7116 = [0, 0, 169548676143, 471492278260, 258904208197, 19269248429, 0, 0] := by
  decide +kernel

theorem rows7117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7117 = true := by
  decide +kernel

theorem tot7117 : totK PD2M8K2 D2M8K2.t7117 = [0, 39708786304, 214970215382, 418129339425, 214710148836, 12864051566, 0, 0] := by
  decide +kernel

theorem rows7118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7118 = true := by
  decide +kernel

theorem tot7118 : totK PD2M8K2 D2M8K2.t7118 = [0, 207358130355, 485462479280, 194824155997, 9848247143, 0, 0, 0] := by
  decide +kernel

theorem rows7119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7119 = true := by
  decide +kernel

theorem tot7119 : totK PD2M8K2 D2M8K2.t7119 = [0, 170686001626, 460651348433, 241767180674, 13795945806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
