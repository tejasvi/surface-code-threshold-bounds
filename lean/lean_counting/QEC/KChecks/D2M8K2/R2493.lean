import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9972 = true := by
  decide +kernel

theorem tot9972 : totK PD2M8K2 D2M8K2.t9972 = [0, 0, 70190546312, 383594349836, 420768235658, 61328492103, 0, 0] := by
  decide +kernel

theorem rows9973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9973 = true := by
  decide +kernel

theorem tot9973 : totK PD2M8K2 D2M8K2.t9973 = [0, 0, 86950764009, 291208080855, 376989516734, 132211908931, 5348807592, 0] := by
  decide +kernel

theorem rows9974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9974 = true := by
  decide +kernel

theorem tot9974 : totK PD2M8K2 D2M8K2.t9974 = [0, 0, 178717971016, 472280511200, 256725569493, 20246149729, 0, 0] := by
  decide +kernel

theorem rows9975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9975 = true := by
  decide +kernel

theorem tot9975 : totK PD2M8K2 D2M8K2.t9975 = [0, 0, 173689089073, 465372652006, 248005271583, 13782265251, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
