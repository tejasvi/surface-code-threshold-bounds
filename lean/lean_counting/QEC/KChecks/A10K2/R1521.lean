import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6084 = true := by
  decide +kernel

theorem tot6084 : totK PA10K2 A10K2.t6084 = [0, 504782908657, 1790475113989, 2036008776764, 742996279567, 71001312818, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6085 = true := by
  decide +kernel

theorem tot6085 : totK PA10K2 A10K2.t6085 = [0, 320625971501, 1509647739103, 2217365384367, 1056414501276, 106999039679, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6086 = true := by
  decide +kernel

theorem tot6086 : totK PA10K2 A10K2.t6086 = [0, 0, 605727928085, 2078523453823, 1991176251885, 425782033257, 13242594235, 0, 0, 0] := by
  decide +kernel

theorem rows6087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6087 = true := by
  decide +kernel

theorem tot6087 : totK PA10K2 A10K2.t6087 = [0, 0, 378164680992, 1521411055920, 2067720691456, 868104085805, 75177836158, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
