import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12832 = true := by
  decide +kernel

theorem tot12832 : totK PD2M8K2 D2M8K2.t12832 = [0, 179637077310, 445091679679, 262126542862, 21008068134, 0, 0, 0] := by
  decide +kernel

theorem rows12833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12833 = true := by
  decide +kernel

theorem tot12833 : totK PD2M8K2 D2M8K2.t12833 = [0, 67666276829, 347296460155, 383983426307, 78725478870, 1164319620, 0, 0] := by
  decide +kernel

theorem rows12834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12834 = true := by
  decide +kernel

theorem tot12834 : totK PD2M8K2 D2M8K2.t12834 = [0, 0, 231475664080, 487404052294, 160632029855, 9404247146, 0, 0] := by
  decide +kernel

theorem rows12835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12835 = true := by
  decide +kernel

theorem tot12835 : totK PD2M8K2 D2M8K2.t12835 = [0, 166594156294, 405469097309, 258104090866, 57758938939, 2481160468, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
