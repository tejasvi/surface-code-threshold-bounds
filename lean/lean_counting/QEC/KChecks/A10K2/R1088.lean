import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4352 = true := by
  decide +kernel

theorem tot4352 : totK PA10K2 A10K2.t4352 = [0, 0, 199092214397, 409627046024, 859735121690, 1770866242270, 1070741162547, 171735004960, 5676195732, 0] := by
  decide +kernel

theorem rows4353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4353 = true := by
  decide +kernel

theorem tot4353 : totK PA10K2 A10K2.t4353 = [0, 0, 488028467762, 1861224211451, 1939070300685, 520667709036, 31301336365, 0, 0, 0] := by
  decide +kernel

theorem rows4354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4354 = true := by
  decide +kernel

theorem tot4354 : totK PA10K2 A10K2.t4354 = [0, 0, 118334424620, 963679085078, 2137080694583, 1431771626619, 276014893758, 20058242317, 0, 0] := by
  decide +kernel

theorem rows4355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4355 = true := by
  decide +kernel

theorem tot4355 : totK PA10K2 A10K2.t4355 = [0, 0, 280443219282, 1413656270205, 2205876824832, 1032689870012, 103135932442, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
