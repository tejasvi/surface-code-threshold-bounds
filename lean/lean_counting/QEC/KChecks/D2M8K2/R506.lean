import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2024 = true := by
  decide +kernel

theorem tot2024 : totK PD2M8K2 D2M8K2.t2024 = [0, 0, 170711992347, 462002578678, 238641950633, 13621712409, 0, 0] := by
  decide +kernel

theorem rows2025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2025 = true := by
  decide +kernel

theorem tot2025 : totK PD2M8K2 D2M8K2.t2025 = [0, 0, 0, 295187959052, 475531482310, 85407270701, 1239866073, 0] := by
  decide +kernel

theorem rows2026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2026 = true := by
  decide +kernel

theorem tot2026 : totK PD2M8K2 D2M8K2.t2026 = [0, 0, 110986046468, 396420919303, 356105256061, 38844866066, 0, 0] := by
  decide +kernel

theorem rows2027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2027 = true := by
  decide +kernel

theorem tot2027 : totK PD2M8K2 D2M8K2.t2027 = [0, 0, 207658876948, 484851281590, 200685653172, 9703098049, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
