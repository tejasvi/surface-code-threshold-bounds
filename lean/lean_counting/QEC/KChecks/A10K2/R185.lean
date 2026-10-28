import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t740 = true := by
  decide +kernel

theorem tot740 : totK PA10K2 A10K2.t740 = [454270124658, 1791792707309, 2025032688460, 573452907001, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t741 = true := by
  decide +kernel

theorem tot741 : totK PA10K2 A10K2.t741 = [71242736739, 912538928975, 2062739956404, 1552805897931, 378214310997, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t742 = true := by
  decide +kernel

theorem tot742 : totK PA10K2 A10K2.t742 = [278476457782, 1158842234058, 1904745327503, 1295096487057, 215318339478, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t743 = true := by
  decide +kernel

theorem tot743 : totK PA10K2 A10K2.t743 = [462546665082, 1705852466877, 1886685003036, 624469368126, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
