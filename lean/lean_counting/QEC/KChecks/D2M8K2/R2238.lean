import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8952 = true := by
  decide +kernel

theorem tot8952 : totK PD2M8K2 D2M8K2.t8952 = [163690086331, 390765031957, 242983034572, 91033370604, 6627249222, 0, 0, 0] := by
  decide +kernel

theorem rows8953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8953 = true := by
  decide +kernel

theorem tot8953 : totK PD2M8K2 D2M8K2.t8953 = [159843008701, 453785749857, 266328812849, 19328962636, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8954 = true := by
  decide +kernel

theorem tot8954 : totK PD2M8K2 D2M8K2.t8954 = [0, 215249584751, 486343379071, 163196479960, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows8955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8955 = true := by
  decide +kernel

theorem tot8955 : totK PD2M8K2 D2M8K2.t8955 = [122008031799, 357599262215, 307023163183, 86087053922, 5883432551, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
