import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13416 = true := by
  decide +kernel

theorem tot13416 : totK PD2M8K2 D2M8K2.t13416 = [0, 0, 0, 174557946628, 464390636804, 221076814894, 13026650529, 0] := by
  decide +kernel

theorem rows13417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13417 = true := by
  decide +kernel

theorem tot13417 : totK PD2M8K2 D2M8K2.t13417 = [0, 0, 0, 304457306885, 500480951736, 81297725944, 1369587937, 0] := by
  decide +kernel

theorem rows13418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13418 = true := by
  decide +kernel

theorem tot13418 : totK PD2M8K2 D2M8K2.t13418 = [0, 0, 181982747135, 447541211355, 279162529189, 28066614179, 0, 0] := by
  decide +kernel

theorem rows13419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13419 = true := by
  decide +kernel

theorem tot13419 : totK PD2M8K2 D2M8K2.t13419 = [0, 0, 175950188653, 482238339105, 239164968547, 9940310632, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
