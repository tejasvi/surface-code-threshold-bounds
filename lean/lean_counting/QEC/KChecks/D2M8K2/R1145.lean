import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4580 = true := by
  decide +kernel

theorem tot4580 : totK PD2M8K2 D2M8K2.t4580 = [0, 0, 176333444930, 480702713482, 240758223512, 13535101234, 0, 0] := by
  decide +kernel

theorem rows4581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4581 = true := by
  decide +kernel

theorem tot4581 : totK PD2M8K2 D2M8K2.t4581 = [0, 0, 0, 280216637645, 509515001629, 110029262821, 1164319620, 0] := by
  decide +kernel

theorem rows4582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4582 = true := by
  decide +kernel

theorem tot4582 : totK PD2M8K2 D2M8K2.t4582 = [0, 0, 11177230158, 196726893233, 470375499849, 190046513922, 11885407614, 0] := by
  decide +kernel

theorem rows4583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4583 = true := by
  decide +kernel

theorem tot4583 : totK PD2M8K2 D2M8K2.t4583 = [0, 0, 174776855535, 451723302466, 237790580487, 22744859262, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
