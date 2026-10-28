import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9824 = true := by
  decide +kernel

theorem tot9824 : totK PD2M8K2 D2M8K2.t9824 = [0, 0, 277626294457, 513965111053, 108981730261, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9825 = true := by
  decide +kernel

theorem tot9825 : totK PD2M8K2 D2M8K2.t9825 = [0, 179645629122, 428511893646, 293328038945, 36647590112, 0, 0, 0] := by
  decide +kernel

theorem rows9826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9826 = true := by
  decide +kernel

theorem tot9826 : totK PD2M8K2 D2M8K2.t9826 = [0, 167807221222, 474581936110, 250393117008, 13672237646, 0, 0, 0] := by
  decide +kernel

theorem rows9827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9827 = true := by
  decide +kernel

theorem tot9827 : totK PD2M8K2 D2M8K2.t9827 = [0, 0, 223473460046, 474069727020, 205717426261, 19138396551, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
