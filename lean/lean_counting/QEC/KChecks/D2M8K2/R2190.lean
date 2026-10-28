import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8760 = true := by
  decide +kernel

theorem tot8760 : totK PD2M8K2 D2M8K2.t8760 = [0, 0, 182210025958, 468701462866, 246909344482, 19854384913, 0, 0] := by
  decide +kernel

theorem rows8761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8761 = true := by
  decide +kernel

theorem tot8761 : totK PD2M8K2 D2M8K2.t8761 = [0, 0, 171806588035, 459079137598, 239426211306, 13544328103, 0, 0] := by
  decide +kernel

theorem rows8762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8762 = true := by
  decide +kernel

theorem tot8762 : totK PD2M8K2 D2M8K2.t8762 = [0, 0, 0, 303054532498, 483901205939, 97182709354, 3017543995, 0] := by
  decide +kernel

theorem rows8763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8763 = true := by
  decide +kernel

theorem tot8763 : totK PD2M8K2 D2M8K2.t8763 = [0, 0, 76423586190, 298683600089, 370909782800, 100245735494, 2335238446, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
