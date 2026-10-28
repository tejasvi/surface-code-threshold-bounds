import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6684 = true := by
  decide +kernel

theorem tot6684 : totK PA10K2 A10K2.t6684 = [0, 0, 664924849657, 2001459312999, 1687518331518, 394253801852, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows6685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6685 = true := by
  decide +kernel

theorem tot6685 : totK PA10K2 A10K2.t6685 = [0, 287804590978, 1230132741972, 1903895497824, 1108751166116, 184096786431, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows6686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6686 = true := by
  decide +kernel

theorem tot6686 : totK PA10K2 A10K2.t6686 = [0, 294676414176, 1450564375206, 2051431344712, 763078581910, 58478816748, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6687 = true := by
  decide +kernel

theorem tot6687 : totK PA10K2 A10K2.t6687 = [0, 297510539734, 1263485019870, 1870025346661, 1104256988835, 173790711660, 5705019915, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
