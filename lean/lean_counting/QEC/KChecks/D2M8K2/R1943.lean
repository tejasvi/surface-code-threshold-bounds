import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7772 = true := by
  decide +kernel

theorem tot7772 : totK PD2M8K2 D2M8K2.t7772 = [0, 0, 60425529563, 338789315169, 425006784448, 82400774386, 1164319620, 0] := by
  decide +kernel

theorem rows7773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7773 = true := by
  decide +kernel

theorem tot7773 : totK PD2M8K2 D2M8K2.t7773 = [0, 0, 0, 270990145968, 498698338655, 129969583652, 6000995271, 0] := by
  decide +kernel

theorem rows7774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7774 = true := by
  decide +kernel

theorem tot7774 : totK PD2M8K2 D2M8K2.t7774 = [0, 0, 198296515716, 457094745528, 233208955055, 26620223342, 0, 0] := by
  decide +kernel

theorem rows7775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7775 = true := by
  decide +kernel

theorem tot7775 : totK PD2M8K2 D2M8K2.t7775 = [0, 0, 212902637613, 481480665918, 211176809562, 14944747389, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
