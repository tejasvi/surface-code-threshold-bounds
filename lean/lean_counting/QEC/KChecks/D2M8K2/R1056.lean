import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4224 = true := by
  decide +kernel

theorem tot4224 : totK PD2M8K2 D2M8K2.t4224 = [0, 0, 0, 187495412337, 473098569920, 214667936225, 9039890340, 0] := by
  decide +kernel

theorem rows4225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4225 = true := by
  decide +kernel

theorem tot4225 : totK PD2M8K2 D2M8K2.t4225 = [0, 0, 0, 19373123746, 363470518397, 457807117353, 55068428376, 0] := by
  decide +kernel

theorem rows4226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4226 = true := by
  decide +kernel

theorem tot4226 : totK PD2M8K2 D2M8K2.t4226 = [0, 0, 0, 65231844053, 246776542631, 407940879566, 131912576913, 5067863418] := by
  decide +kernel

theorem rows4227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4227 = true := by
  decide +kernel

theorem tot4227 : totK PD2M8K2 D2M8K2.t4227 = [0, 0, 0, 181715041632, 465870925018, 248794736495, 21890168488, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
