import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1944 = true := by
  decide +kernel

theorem tot1944 : totK PA10K2 A10K2.t1944 = [0, 0, 0, 610352461647, 2127443379947, 1959916021101, 362155966444, 6962742351, 0, 0] := by
  decide +kernel

theorem rows1945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1945 = true := by
  decide +kernel

theorem tot1945 : totK PA10K2 A10K2.t1945 = [0, 415295505255, 1323007942973, 1265815047120, 619115509916, 756969168972, 456626516297, 49137922124, 0, 0] := by
  decide +kernel

theorem rows1946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1946 = true := by
  decide +kernel

theorem tot1946 : totK PA10K2 A10K2.t1946 = [0, 404480103954, 1714876041843, 2055525875991, 723999543374, 57381182088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1947 = true := by
  decide +kernel

theorem tot1947 : totK PA10K2 A10K2.t1947 = [0, 0, 477749092486, 1831430145548, 1809841795205, 455764293123, 25371180993, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
