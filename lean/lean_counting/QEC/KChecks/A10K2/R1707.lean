import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6828 = true := by
  decide +kernel

theorem tot6828 : totK PA10K2 A10K2.t6828 = [0, 17179869184, 896043278460, 2260340690416, 1561603558675, 244681154939, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows6829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6829 = true := by
  decide +kernel

theorem tot6829 : totK PA10K2 A10K2.t6829 = [0, 0, 496006671583, 1900120237950, 2021763965890, 506290971434, 17732757243, 0, 0, 0] := by
  decide +kernel

theorem rows6830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6830 = true := by
  decide +kernel

theorem tot6830 : totK PA10K2 A10K2.t6830 = [0, 510168469446, 1687524669054, 1601572708568, 641362546835, 243877430804, 37310410385, 0, 0, 0] := by
  decide +kernel

theorem rows6831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6831 = true := by
  decide +kernel

theorem tot6831 : totK PA10K2 A10K2.t6831 = [0, 296752361392, 1463770793998, 2175939994141, 910454870701, 76765372953, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
