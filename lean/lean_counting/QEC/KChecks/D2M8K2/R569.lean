import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2276 = true := by
  decide +kernel

theorem tot2276 : totK PD2M8K2 D2M8K2.t2276 = [0, 11085913658, 195241962842, 464613074226, 184614095475, 11885407614, 0, 0] := by
  decide +kernel

theorem rows2277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2277 = true := by
  decide +kernel

theorem tot2277 : totK PD2M8K2 D2M8K2.t2277 = [0, 195887879199, 466208965957, 222064345454, 19621842483, 0, 0, 0] := by
  decide +kernel

theorem rows2278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2278 = true := by
  decide +kernel

theorem tot2278 : totK PD2M8K2 D2M8K2.t2278 = [0, 194220622149, 464849334308, 218778856508, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows2279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2279 = true := by
  decide +kernel

theorem tot2279 : totK PD2M8K2 D2M8K2.t2279 = [0, 8125304319, 300183055818, 480927952227, 104331258113, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
