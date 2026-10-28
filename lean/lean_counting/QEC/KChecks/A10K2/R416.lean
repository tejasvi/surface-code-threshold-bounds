import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1664 = true := by
  decide +kernel

theorem tot1664 : totK PA10K2 A10K2.t1664 = [0, 250867552997, 868023794505, 1295047238056, 1361515849003, 824802770004, 161460762868, 6121173289, 0, 0] := by
  decide +kernel

theorem rows1665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1665 = true := by
  decide +kernel

theorem tot1665 : totK PA10K2 A10K2.t1665 = [0, 428225544449, 1739546934351, 1999158398986, 565735049550, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1666 = true := by
  decide +kernel

theorem tot1666 : totK PA10K2 A10K2.t1666 = [0, 67600016556, 794366705764, 1960720136131, 1549484703403, 385221374584, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows1667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1667 = true := by
  decide +kernel

theorem tot1667 : totK PA10K2 A10K2.t1667 = [0, 283150731151, 1180059743013, 1865311366774, 1163591104431, 196623930802, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
