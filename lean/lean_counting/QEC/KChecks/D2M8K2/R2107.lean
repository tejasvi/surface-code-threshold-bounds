import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8428 = true := by
  decide +kernel

theorem tot8428 : totK PD2M8K2 D2M8K2.t8428 = [0, 29363365677, 276146596367, 470732722938, 110896032715, 3820764243, 0, 0] := by
  decide +kernel

theorem rows8429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8429 = true := by
  decide +kernel

theorem tot8429 : totK PD2M8K2 D2M8K2.t8429 = [0, 194435289516, 462243441374, 230624090833, 19845724376, 0, 0, 0] := by
  decide +kernel

theorem rows8430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8430 = true := by
  decide +kernel

theorem tot8430 : totK PD2M8K2 D2M8K2.t8430 = [0, 178807734416, 475151111701, 242582023472, 13790854450, 0, 0, 0] := by
  decide +kernel

theorem rows8431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8431 = true := by
  decide +kernel

theorem tot8431 : totK PD2M8K2 D2M8K2.t8431 = [0, 0, 283165626870, 496409571862, 112629246280, 1232398321, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
