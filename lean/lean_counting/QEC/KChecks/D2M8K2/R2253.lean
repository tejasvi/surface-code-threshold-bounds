import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9012 = true := by
  decide +kernel

theorem tot9012 : totK PD2M8K2 D2M8K2.t9012 = [0, 93578448888, 356631466285, 368496205795, 72567121161, 1242138600, 0, 0] := by
  decide +kernel

theorem rows9013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9013 = true := by
  decide +kernel

theorem tot9013 : totK PD2M8K2 D2M8K2.t9013 = [0, 0, 255134685312, 482131424616, 135270204439, 3569676519, 0, 0] := by
  decide +kernel

theorem rows9014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9014 = true := by
  decide +kernel

theorem tot9014 : totK PD2M8K2 D2M8K2.t9014 = [0, 92082099022, 258569519705, 340092232730, 179225652805, 15908383818, 0, 0] := by
  decide +kernel

theorem rows9015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9015 = true := by
  decide +kernel

theorem tot9015 : totK PD2M8K2 D2M8K2.t9015 = [0, 169409538281, 471191500846, 233185761461, 14446343679, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
