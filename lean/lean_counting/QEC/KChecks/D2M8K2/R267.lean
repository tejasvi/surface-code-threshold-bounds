import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1068 = true := by
  decide +kernel

theorem tot1068 : totK PD2M8K2 D2M8K2.t1068 = [0, 0, 271410064096, 506267115807, 109122422006, 1164319620, 0, 0] := by
  decide +kernel

theorem rows1069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1069 = true := by
  decide +kernel

theorem tot1069 : totK PD2M8K2 D2M8K2.t1069 = [0, 51606794757, 241810041312, 406666641736, 155412209734, 11819130176, 0, 0] := by
  decide +kernel

theorem rows1070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1070 = true := by
  decide +kernel

theorem tot1070 : totK PD2M8K2 D2M8K2.t1070 = [0, 190611942381, 477938069523, 225038311669, 12428298885, 0, 0, 0] := by
  decide +kernel

theorem rows1071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1071 = true := by
  decide +kernel

theorem tot1071 : totK PD2M8K2 D2M8K2.t1071 = [0, 164922019037, 464091964818, 246515553645, 13782265251, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
