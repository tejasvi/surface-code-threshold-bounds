import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13988 = true := by
  decide +kernel

theorem tot13988 : totK PD2M8K2 D2M8K2.t13988 = [0, 0, 0, 341128200843, 503627882629, 53849426189, 0, 0] := by
  decide +kernel

theorem rows13989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13989 = true := by
  decide +kernel

theorem tot13989 : totK PD2M8K2 D2M8K2.t13989 = [0, 0, 157141031770, 389759515244, 288223239283, 69499218807, 1392055030, 0] := by
  decide +kernel

theorem rows13990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13990 = true := by
  decide +kernel

theorem tot13990 : totK PD2M8K2 D2M8K2.t13990 = [0, 0, 170935876734, 433432380091, 263885974280, 26962658215, 0, 0] := by
  decide +kernel

theorem rows13991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13991 = true := by
  decide +kernel

theorem tot13991 : totK PD2M8K2 D2M8K2.t13991 = [0, 0, 91986061513, 430153863281, 346060574622, 34691941931, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
