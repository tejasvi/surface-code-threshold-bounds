import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4792 = true := by
  decide +kernel

theorem tot4792 : totK PD2M8K2 D2M8K2.t4792 = [0, 55729936123, 285157669598, 380791124490, 176597608363, 21379892652, 0, 0] := by
  decide +kernel

theorem rows4793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4793 = true := by
  decide +kernel

theorem tot4793 : totK PD2M8K2 D2M8K2.t4793 = [0, 0, 204845060881, 486567902144, 208699236709, 7960855803, 0, 0] := by
  decide +kernel

theorem rows4794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4794 = true := by
  decide +kernel

theorem tot4794 : totK PD2M8K2 D2M8K2.t4794 = [0, 67193450784, 272032597480, 381982612508, 172156828687, 8213711289, 0, 0] := by
  decide +kernel

theorem rows4795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4795 = true := by
  decide +kernel

theorem tot4795 : totK PD2M8K2 D2M8K2.t4795 = [0, 173867466881, 448921111250, 278454660004, 28865649823, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
