import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5952 = true := by
  decide +kernel

theorem tot5952 : totK PA10K2 A10K2.t5952 = [0, 0, 468940266771, 1745361088173, 1919693929312, 513900165998, 31222411477, 0, 0, 0] := by
  decide +kernel

theorem rows5953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5953 = true := by
  decide +kernel

theorem tot5953 : totK PA10K2 A10K2.t5953 = [0, 0, 176299232005, 1069464847649, 1959346406459, 1260559168802, 291410716356, 20060612110, 0, 0] := by
  decide +kernel

theorem rows5954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5954 = true := by
  decide +kernel

theorem tot5954 : totK PA10K2 A10K2.t5954 = [0, 0, 211054698099, 1003669012575, 1830497501489, 1256809788326, 253025755256, 10545135740, 0, 0] := by
  decide +kernel

theorem rows5955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5955 = true := by
  decide +kernel

theorem tot5955 : totK PA10K2 A10K2.t5955 = [0, 0, 463199241479, 1727759949242, 1783241962589, 467263501954, 30954851499, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
