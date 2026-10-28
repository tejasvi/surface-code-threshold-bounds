import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9916 = true := by
  decide +kernel

theorem tot9916 : totK PD2M8K2 D2M8K2.t9916 = [0, 0, 204863900139, 484640327526, 212107095430, 10502486720, 0, 0] := by
  decide +kernel

theorem rows9917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9917 = true := by
  decide +kernel

theorem tot9917 : totK PD2M8K2 D2M8K2.t9917 = [0, 0, 173081379926, 451584979090, 267055222146, 22974852597, 0, 0] := by
  decide +kernel

theorem rows9918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9918 = true := by
  decide +kernel

theorem tot9918 : totK PD2M8K2 D2M8K2.t9918 = [0, 0, 106826467550, 407904199156, 336398332499, 32647977159, 0, 0] := by
  decide +kernel

theorem rows9919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9919 = true := by
  decide +kernel

theorem tot9919 : totK PD2M8K2 D2M8K2.t9919 = [0, 0, 0, 262455224439, 464228194104, 129905602144, 4931404646, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
