import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3584 = true := by
  decide +kernel

theorem tot3584 : totK PD2M8K2 D2M8K2.t3584 = [0, 185439479441, 471976928095, 223658328112, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows3585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3585 = true := by
  decide +kernel

theorem tot3585 : totK PD2M8K2 D2M8K2.t3585 = [0, 4187820809, 297398094214, 489065105156, 97550012910, 1198073392, 0, 0] := by
  decide +kernel

theorem rows3586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3586 = true := by
  decide +kernel

theorem tot3586 : totK PD2M8K2 D2M8K2.t3586 = [0, 18600924932, 201594302205, 453302821155, 177517284090, 11986244008, 0, 0] := by
  decide +kernel

theorem rows3587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3587 = true := by
  decide +kernel

theorem tot3587 : totK PD2M8K2 D2M8K2.t3587 = [0, 193578409424, 466821204028, 225947189762, 16192212756, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
