import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3596 = true := by
  decide +kernel

theorem tot3596 : totK PD2M8K2 D2M8K2.t3596 = [0, 0, 248110628330, 502656505541, 142800780500, 2530668022, 0, 0] := by
  decide +kernel

theorem rows3597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3597 = true := by
  decide +kernel

theorem tot3597 : totK PD2M8K2 D2M8K2.t3597 = [0, 0, 217490815007, 473552747086, 177581547637, 11092222415, 0, 0] := by
  decide +kernel

theorem rows3598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3598 = true := by
  decide +kernel

theorem tot3598 : totK PD2M8K2 D2M8K2.t3598 = [0, 0, 175836548835, 482513342908, 203153300934, 7106801134, 0, 0] := by
  decide +kernel

theorem rows3599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3599 = true := by
  decide +kernel

theorem tot3599 : totK PD2M8K2 D2M8K2.t3599 = [0, 0, 175198413340, 469650868926, 211778022706, 13026650529, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
