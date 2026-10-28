import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5044 = true := by
  decide +kernel

theorem tot5044 : totK PD2M8K2 D2M8K2.t5044 = [0, 184165120029, 463539232908, 252738082556, 23048968184, 0, 0, 0] := by
  decide +kernel

theorem rows5045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5045 = true := by
  decide +kernel

theorem tot5045 : totK PD2M8K2 D2M8K2.t5045 = [0, 192517351675, 479210762205, 225090683133, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows5046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5046 = true := by
  decide +kernel

theorem tot5046 : totK PD2M8K2 D2M8K2.t5046 = [0, 8125304319, 295518388715, 483797615624, 100958675491, 1198073392, 0, 0] := by
  decide +kernel

theorem rows5047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5047 = true := by
  decide +kernel

theorem tot5047 : totK PD2M8K2 D2M8K2.t5047 = [0, 0, 195004791832, 473000268366, 199257483793, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
