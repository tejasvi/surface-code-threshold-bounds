import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9584 = true := by
  decide +kernel

theorem tot9584 : totK PD2M8K2 D2M8K2.t9584 = [163061422320, 434732029866, 272013705575, 29924697252, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9585 = true := by
  decide +kernel

theorem tot9585 : totK PD2M8K2 D2M8K2.t9585 = [125598274321, 429934040722, 317290908801, 27715507500, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9586 = true := by
  decide +kernel

theorem tot9586 : totK PD2M8K2 D2M8K2.t9586 = [0, 209724576040, 476954132402, 177787033054, 9480173171, 0, 0, 0] := by
  decide +kernel

theorem rows9587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9587 = true := by
  decide +kernel

theorem tot9587 : totK PD2M8K2 D2M8K2.t9587 = [122297332964, 379885743852, 324881684986, 67791890540, 980350181, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
