import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t204 = true := by
  decide +kernel

theorem tot204 : totK PA10K2 A10K2.t204 = [0, 42628046239, 362273330340, 1586083479939, 2163385048057, 829692493658, 62632138461, 0, 0, 0] := by
  decide +kernel

theorem rows205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t205 = true := by
  decide +kernel

theorem tot205 : totK PA10K2 A10K2.t205 = [0, 539407736445, 1951925542381, 1879020839455, 443832980971, 25523588264, 0, 0, 0, 0] := by
  decide +kernel

theorem rows206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t206 = true := by
  decide +kernel

theorem tot206 : totK PA10K2 A10K2.t206 = [0, 199903282695, 1145713285025, 2103562253613, 1279465144117, 243499217603, 11991740650, 0, 0, 0] := by
  decide +kernel

theorem rows207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t207 = true := by
  decide +kernel

theorem tot207 : totK PA10K2 A10K2.t207 = [0, 254943197349, 1098961016998, 1931233606067, 1409113179949, 223121589508, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
