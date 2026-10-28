import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4056 = true := by
  decide +kernel

theorem tot4056 : totK PA10K2 A10K2.t4056 = [0, 0, 176592419349, 1120276769098, 2097990556309, 1189168550752, 184507413786, 6239673734, 0, 0] := by
  decide +kernel

theorem rows4057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4057 = true := by
  decide +kernel

theorem tot4057 : totK PA10K2 A10K2.t4057 = [0, 0, 499380135405, 1871739966369, 2038163899416, 598021714236, 37639722833, 0, 0, 0] := by
  decide +kernel

theorem rows4058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4058 = true := by
  decide +kernel

theorem tot4058 : totK PA10K2 A10K2.t4058 = [0, 0, 227740758055, 1187778930298, 2117944564898, 1400343141817, 246841182743, 6279851884, 0, 0] := by
  decide +kernel

theorem rows4059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4059 = true := by
  decide +kernel

theorem tot4059 : totK PA10K2 A10K2.t4059 = [0, 0, 0, 570097842466, 2058795769963, 1947674728309, 439100382887, 12807360706, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
