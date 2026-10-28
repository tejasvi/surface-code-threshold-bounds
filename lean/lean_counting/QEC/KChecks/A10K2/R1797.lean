import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7188 = true := by
  decide +kernel

theorem tot7188 : totK PA10K2 A10K2.t7188 = [0, 0, 470231141205, 1779685268299, 1900772857862, 543529789698, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows7189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7189 = true := by
  decide +kernel

theorem tot7189 : totK PA10K2 A10K2.t7189 = [0, 0, 571889676104, 1991687706536, 1920312281042, 429880193757, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows7190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7190 = true := by
  decide +kernel

theorem tot7190 : totK PA10K2 A10K2.t7190 = [0, 0, 490723553821, 1816013795512, 1914337758303, 502284308923, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows7191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7191 = true := by
  decide +kernel

theorem tot7191 : totK PA10K2 A10K2.t7191 = [0, 0, 461962242134, 1647871631439, 1909894541430, 579625038167, 50267370225, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
