import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4132 = true := by
  decide +kernel

theorem tot4132 : totK PD2M8K2 D2M8K2.t4132 = [0, 0, 237834645053, 452289412980, 198991808523, 21396654552, 0, 0] := by
  decide +kernel

theorem rows4133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4133 = true := by
  decide +kernel

theorem tot4133 : totK PD2M8K2 D2M8K2.t4133 = [0, 0, 175758509236, 492375979042, 223368811861, 7994456143, 0, 0] := by
  decide +kernel

theorem rows4134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4134 = true := by
  decide +kernel

theorem tot4134 : totK PD2M8K2 D2M8K2.t4134 = [0, 113929913652, 312242315972, 309208863089, 147532260706, 8210597527, 0, 0] := by
  decide +kernel

theorem rows4135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4135 = true := by
  decide +kernel

theorem tot4135 : totK PD2M8K2 D2M8K2.t4135 = [0, 166942518675, 442179748550, 274949261898, 30368503698, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
