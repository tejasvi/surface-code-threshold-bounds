import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6384 = true := by
  decide +kernel

theorem tot6384 : totK PA10K2 A10K2.t6384 = [0, 0, 556996927082, 1995504339886, 1699979677370, 357820186211, 24614390653, 0, 0, 0] := by
  decide +kernel

theorem rows6385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6385 = true := by
  decide +kernel

theorem tot6385 : totK PA10K2 A10K2.t6385 = [0, 580247490663, 1832797088562, 1637096121894, 596455635715, 107173596197, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows6386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6386 = true := by
  decide +kernel

theorem tot6386 : totK PA10K2 A10K2.t6386 = [0, 186511936084, 1261284613631, 2259655597923, 1089469699463, 98752194833, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6387 = true := by
  decide +kernel

theorem tot6387 : totK PA10K2 A10K2.t6387 = [0, 101734305160, 723756209218, 1827060743863, 1572950902699, 389421558371, 31003444686, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
