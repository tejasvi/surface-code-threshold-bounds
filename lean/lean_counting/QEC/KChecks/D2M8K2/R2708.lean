import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10832 = true := by
  decide +kernel

theorem tot10832 : totK PD2M8K2 D2M8K2.t10832 = [0, 0, 200109079068, 469232630709, 235168151730, 17305939744, 0, 0] := by
  decide +kernel

theorem rows10833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10833 = true := by
  decide +kernel

theorem tot10833 : totK PD2M8K2 D2M8K2.t10833 = [0, 0, 37109909677, 407007817050, 432156208827, 48056030082, 0, 0] := by
  decide +kernel

theorem rows10834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10834 = true := by
  decide +kernel

theorem tot10834 : totK PD2M8K2 D2M8K2.t10834 = [0, 0, 161133986086, 382414345015, 292363589193, 65087405144, 1415142070, 0] := by
  decide +kernel

theorem rows10835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10835 = true := by
  decide +kernel

theorem tot10835 : totK PD2M8K2 D2M8K2.t10835 = [0, 0, 167719848094, 442481784239, 272769649671, 26865717750, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
