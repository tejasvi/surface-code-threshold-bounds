import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7604 = true := by
  decide +kernel

theorem tot7604 : totK PA10K2 A10K2.t7604 = [0, 0, 466950596060, 1543566251734, 1609846807100, 821499006324, 339097803414, 43720954405, 0, 0] := by
  decide +kernel

theorem rows7605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7605 = true := by
  decide +kernel

theorem tot7605 : totK PA10K2 A10K2.t7605 = [0, 0, 357308224198, 1648614686526, 2114887966247, 792960775078, 71490345735, 0, 0, 0] := by
  decide +kernel

theorem rows7606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7606 = true := by
  decide +kernel

theorem tot7606 : totK PA10K2 A10K2.t7606 = [0, 0, 0, 463405775719, 1755543158609, 1843361954647, 493489773030, 31306924438, 0, 0] := by
  decide +kernel

theorem rows7607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7607 = true := by
  decide +kernel

theorem tot7607 : totK PA10K2 A10K2.t7607 = [0, 0, 423713582285, 1559058509895, 1974187861315, 892867086480, 91376490771, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
