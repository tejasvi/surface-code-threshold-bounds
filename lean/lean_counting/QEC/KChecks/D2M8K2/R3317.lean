import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13268 = true := by
  decide +kernel

theorem tot13268 : totK PD2M8K2 D2M8K2.t13268 = [0, 0, 176075370610, 453758171971, 271890221423, 18024375274, 0, 0] := by
  decide +kernel

theorem rows13269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13269 = true := by
  decide +kernel

theorem tot13269 : totK PD2M8K2 D2M8K2.t13269 = [0, 0, 172584954749, 480429081510, 247861287034, 11145913502, 0, 0] := by
  decide +kernel

theorem rows13270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13270 = true := by
  decide +kernel

theorem tot13270 : totK PD2M8K2 D2M8K2.t13270 = [0, 0, 0, 201244419612, 468458834130, 210361675724, 17461266593, 0] := by
  decide +kernel

theorem rows13271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13271 = true := by
  decide +kernel

theorem tot13271 : totK PD2M8K2 D2M8K2.t13271 = [0, 0, 0, 208701341427, 478374802015, 187047488611, 6265814000, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
