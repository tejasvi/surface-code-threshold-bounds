import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9092 = true := by
  decide +kernel

theorem tot9092 : totK PD2M8K2 D2M8K2.t9092 = [0, 0, 185908728177, 461817288697, 235428189405, 15373477478, 0, 0] := by
  decide +kernel

theorem rows9093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9093 = true := by
  decide +kernel

theorem tot9093 : totK PD2M8K2 D2M8K2.t9093 = [0, 0, 76795458081, 352787732967, 370978281587, 78714472408, 1171084559, 0] := by
  decide +kernel

theorem rows9094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9094 = true := by
  decide +kernel

theorem tot9094 : totK PD2M8K2 D2M8K2.t9094 = [0, 0, 0, 209283259063, 468078742176, 169468764183, 9444064503, 0] := by
  decide +kernel

theorem rows9095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9095 = true := by
  decide +kernel

theorem tot9095 : totK PD2M8K2 D2M8K2.t9095 = [0, 0, 168708100794, 444459646867, 228582989099, 35225237132, 2490301335, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
