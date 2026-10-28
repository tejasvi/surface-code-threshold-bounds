import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5664 = true := by
  decide +kernel

theorem tot5664 : totK PD2M8K2 D2M8K2.t5664 = [0, 0, 260825588831, 484848458507, 121801058186, 3804183361, 0, 0] := by
  decide +kernel

theorem rows5665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5665 = true := by
  decide +kernel

theorem tot5665 : totK PD2M8K2 D2M8K2.t5665 = [0, 151320461696, 441078278807, 287128569792, 33840017641, 0, 0, 0] := by
  decide +kernel

theorem rows5666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5666 = true := by
  decide +kernel

theorem tot5666 : totK PD2M8K2 D2M8K2.t5666 = [0, 202744763275, 446368864412, 214022450264, 16632874163, 0, 0, 0] := by
  decide +kernel

theorem rows5667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5667 = true := by
  decide +kernel

theorem tot5667 : totK PD2M8K2 D2M8K2.t5667 = [0, 26574631215, 323380092838, 453843292089, 78796242784, 1107157161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
