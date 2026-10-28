import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5944 = true := by
  decide +kernel

theorem tot5944 : totK PA10K2 A10K2.t5944 = [0, 440177673483, 1779878751031, 2018737465530, 542138922134, 13032772403, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5945 = true := by
  decide +kernel

theorem tot5945 : totK PA10K2 A10K2.t5945 = [0, 0, 572360036214, 1959663405729, 1721500338422, 415968167048, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5946 = true := by
  decide +kernel

theorem tot5946 : totK PA10K2 A10K2.t5946 = [0, 293535254566, 1277036495157, 1961778717317, 1114103109314, 182672982909, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5947 = true := by
  decide +kernel

theorem tot5947 : totK PA10K2 A10K2.t5947 = [0, 387860993546, 1601491369000, 1856385943276, 573415006484, 38188255074, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
