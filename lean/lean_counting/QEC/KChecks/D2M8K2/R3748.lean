import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14992 = true := by
  decide +kernel

theorem tot14992 : totK PD2M8K2 D2M8K2.t14992 = [0, 0, 247317166293, 469794466867, 147985259958, 7318015431, 0, 0] := by
  decide +kernel

theorem rows14993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14993 = true := by
  decide +kernel

theorem tot14993 : totK PD2M8K2 D2M8K2.t14993 = [0, 0, 180757828158, 481132184017, 195245418300, 7640050840, 0, 0] := by
  decide +kernel

theorem rows14994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14994 = true := by
  decide +kernel

theorem tot14994 : totK PD2M8K2 D2M8K2.t14994 = [0, 0, 196157543110, 468237713862, 219829955492, 15620504087, 0, 0] := by
  decide +kernel

theorem rows14995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14995 = true := by
  decide +kernel

theorem tot14995 : totK PD2M8K2 D2M8K2.t14995 = [0, 78205854702, 221873292491, 363934933665, 215664381277, 17404239282, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
