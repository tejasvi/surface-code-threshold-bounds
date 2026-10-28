import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12616 = true := by
  decide +kernel

theorem tot12616 : totK PD2M8K2 D2M8K2.t12616 = [0, 0, 182923866943, 486914266940, 203747687603, 8669917095, 0, 0] := by
  decide +kernel

theorem rows12617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12617 = true := by
  decide +kernel

theorem tot12617 : totK PD2M8K2 D2M8K2.t12617 = [0, 0, 175776294190, 470791855051, 221489360327, 14631128802, 0, 0] := by
  decide +kernel

theorem rows12618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12618 = true := by
  decide +kernel

theorem tot12618 : totK PD2M8K2 D2M8K2.t12618 = [0, 0, 188066123919, 471208629080, 197417243155, 7913321096, 0, 0] := by
  decide +kernel

theorem rows12619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12619 = true := by
  decide +kernel

theorem tot12619 : totK PD2M8K2 D2M8K2.t12619 = [0, 0, 55661912469, 328874549991, 402995399465, 80008568668, 1310285577, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
