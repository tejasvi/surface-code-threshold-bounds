import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6732 = true := by
  decide +kernel

theorem tot6732 : totK PD2M8K2 D2M8K2.t6732 = [87773917060, 347211953715, 384582184929, 75133573514, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows6733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6733 = true := by
  decide +kernel

theorem tot6733 : totK PD2M8K2 D2M8K2.t6733 = [0, 236940742457, 475592216783, 165026260131, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows6734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6734 = true := by
  decide +kernel

theorem tot6734 : totK PD2M8K2 D2M8K2.t6734 = [141287649189, 398990212510, 295897902572, 62765744746, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows6735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6735 = true := by
  decide +kernel

theorem tot6735 : totK PD2M8K2 D2M8K2.t6735 = [152983603272, 438259316643, 264681452526, 27025993453, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
