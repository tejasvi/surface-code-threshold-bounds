import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5972 = true := by
  decide +kernel

theorem tot5972 : totK PA10K2 A10K2.t5972 = [0, 512075970115, 1889638076637, 2067520816579, 689334509356, 65111967530, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5973 = true := by
  decide +kernel

theorem tot5973 : totK PA10K2 A10K2.t5973 = [0, 212536393063, 1035447607001, 1993603524880, 1553769352856, 296182478917, 7151180950, 0, 0, 0] := by
  decide +kernel

theorem rows5974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5974 = true := by
  decide +kernel

theorem tot5974 : totK PA10K2 A10K2.t5974 = [0, 495962603450, 1884711731105, 2067887310171, 586181349183, 31849442339, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5975 = true := by
  decide +kernel

theorem tot5975 : totK PA10K2 A10K2.t5975 = [0, 122355545644, 980614217056, 2151356562351, 1494384871029, 262541656856, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
