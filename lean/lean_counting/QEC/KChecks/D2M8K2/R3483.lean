import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13932 = true := by
  decide +kernel

theorem tot13932 : totK PD2M8K2 D2M8K2.t13932 = [112776311510, 428463619036, 345216133884, 30198414262, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13933 = true := by
  decide +kernel

theorem tot13933 : totK PD2M8K2 D2M8K2.t13933 = [0, 213250166672, 498246582865, 176580304857, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows13934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13934 = true := by
  decide +kernel

theorem tot13934 : totK PD2M8K2 D2M8K2.t13934 = [0, 192919514992, 463196342577, 220806311653, 17080783126, 0, 0, 0] := by
  decide +kernel

theorem rows13935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13935 = true := by
  decide +kernel

theorem tot13935 : totK PD2M8K2 D2M8K2.t13935 = [0, 204308311658, 491801983802, 195708583394, 5336070015, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
