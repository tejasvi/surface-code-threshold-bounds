import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1032 = true := by
  decide +kernel

theorem tot1032 : totK PD2M8K2 D2M8K2.t1032 = [174869889529, 480385145476, 235704623563, 12066657201, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1033 = true := by
  decide +kernel

theorem tot1033 : totK PD2M8K2 D2M8K2.t1033 = [52730177238, 261761375836, 379654919971, 181720804050, 21273849973, 0, 0, 0] := by
  decide +kernel

theorem rows1034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1034 = true := by
  decide +kernel

theorem tot1034 : totK PD2M8K2 D2M8K2.t1034 = [0, 204706790427, 473044105406, 199171914778, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows1035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1035 = true := by
  decide +kernel

theorem tot1035 : totK PD2M8K2 D2M8K2.t1035 = [96592268210, 292172373775, 345423179529, 144237198195, 3782038083, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
