import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13192 = true := by
  decide +kernel

theorem tot13192 : totK PD2M8K2 D2M8K2.t13192 = [0, 188327899260, 461834575786, 250833987545, 19954862563, 0, 0, 0] := by
  decide +kernel

theorem rows13193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13193 = true := by
  decide +kernel

theorem tot13193 : totK PD2M8K2 D2M8K2.t13193 = [0, 127325337926, 442582148185, 304433921820, 35739133060, 0, 0, 0] := by
  decide +kernel

theorem rows13194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13194 = true := by
  decide +kernel

theorem tot13194 : totK PD2M8K2 D2M8K2.t13194 = [0, 0, 176048849989, 463900023653, 247969893780, 21425655686, 0, 0] := by
  decide +kernel

theorem rows13195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13195 = true := by
  decide +kernel

theorem tot13195 : totK PD2M8K2 D2M8K2.t13195 = [0, 14517969929, 163748937932, 457108534028, 247951445415, 12229515597, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
