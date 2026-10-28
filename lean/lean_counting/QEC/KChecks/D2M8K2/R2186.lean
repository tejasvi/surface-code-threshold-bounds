import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8744 = true := by
  decide +kernel

theorem tot8744 : totK PD2M8K2 D2M8K2.t8744 = [0, 183167185518, 464144778944, 267826686326, 26420265641, 0, 0, 0] := by
  decide +kernel

theorem rows8745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8745 = true := by
  decide +kernel

theorem tot8745 : totK PD2M8K2 D2M8K2.t8745 = [0, 175404056910, 469782211243, 244338161518, 12416698460, 0, 0, 0] := by
  decide +kernel

theorem rows8746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8746 = true := by
  decide +kernel

theorem tot8746 : totK PD2M8K2 D2M8K2.t8746 = [0, 0, 279620505302, 509557064144, 117419141218, 1178750802, 0, 0] := by
  decide +kernel

theorem rows8747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8747 = true := by
  decide +kernel

theorem tot8747 : totK PD2M8K2 D2M8K2.t8747 = [0, 26941954745, 205915948514, 438068934174, 191363820715, 12017349186, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
