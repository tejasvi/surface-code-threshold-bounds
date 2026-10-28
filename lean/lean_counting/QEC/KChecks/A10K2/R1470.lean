import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5880 = true := by
  decide +kernel

theorem tot5880 : totK PA10K2 A10K2.t5880 = [0, 0, 0, 186126909919, 980159750265, 1948617955657, 1291110734693, 240861573251, 6354482628, 0] := by
  decide +kernel

theorem rows5881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5881 = true := by
  decide +kernel

theorem tot5881 : totK PA10K2 A10K2.t5881 = [0, 0, 0, 581142096466, 1976109171338, 1813763634218, 417022619502, 40756708935, 0, 0] := by
  decide +kernel

theorem rows5882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5882 = true := by
  decide +kernel

theorem tot5882 : totK PA10K2 A10K2.t5882 = [0, 0, 0, 490584767793, 1840690421386, 1955052961413, 473107676154, 19117496088, 0, 0] := by
  decide +kernel

theorem rows5883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5883 = true := by
  decide +kernel

theorem tot5883 : totK PA10K2 A10K2.t5883 = [0, 0, 0, 0, 651841813512, 2027766334857, 1554977849093, 346431350591, 25299471099, 0] := by
  decide +kernel

end QECKChecks.A10K2
