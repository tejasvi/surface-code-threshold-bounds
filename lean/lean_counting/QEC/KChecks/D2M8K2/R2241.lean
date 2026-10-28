import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8964 = true := by
  decide +kernel

theorem tot8964 : totK PD2M8K2 D2M8K2.t8964 = [0, 161359709547, 462143794763, 225258066805, 14344490487, 0, 0, 0] := by
  decide +kernel

theorem rows8965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8965 = true := by
  decide +kernel

theorem tot8965 : totK PD2M8K2 D2M8K2.t8965 = [0, 153807637040, 457275141006, 248513484500, 14977982414, 0, 0, 0] := by
  decide +kernel

theorem rows8966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8966 = true := by
  decide +kernel

theorem tot8966 : totK PD2M8K2 D2M8K2.t8966 = [0, 0, 301009836903, 463780877510, 78403596793, 1138244013, 0, 0] := by
  decide +kernel

theorem rows8967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8967 = true := by
  decide +kernel

theorem tot8967 : totK PD2M8K2 D2M8K2.t8967 = [0, 171160256165, 454373739422, 259644066788, 26566298858, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
